from flask import Flask, render_template, redirect, url_for, session
from ManagerFactory import ManagerFactory
from dotenv import load_dotenv
import os

"""
Description:
The App class initializes and manages the central Flask application for the Muscle-Mind platform. It integrates 
backend components for user management, quiz handling, and data analytics, defining routes to handle specific 
functionalities and ensuring a consistent flow for user interactions and backend operations.

Semi-formal Notation:
/*@ requires Environment variables are defined (e.g., SECRET_KEY != null) &&
  @ DatabaseManager, QuizManager, UserManager, DataAnalyticsManager, QuizRetrievalManager are initialized &&
  @ \forall route in { '/', '/add_user', '/login', '/home', ... } (route is valid);
  @ ensures \forall endpoint in self.app.routes (endpoint.method in {"GET", "POST"} && endpoint.handler != null);
@*/
"""
class App:
    
    """
    Description:
    This method initializes the Flask app instance, loads required environment variables, and sets up manager 
    objects. It configures the app to handle sessions, route requests, and perform operations on the database.

    Semi-formal Notation:
    /*@ requires os.getenv("SECRET_KEY") != null &&
    @ load_dotenv() initializes environment variables &&
    @ \forall manager in {DatabaseManager, QuizManager, UserManager, ...} (manager != null);
    @ ensures self.app.config['SECRET_KEY'] == os.getenv('SECRET_KEY') &&
    @ self.db_manager, self.quiz_manager, self.user_manager, ... are instantiated;
    @*/
    """
    def __init__(self):
        load_dotenv()
        self.app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
        self.app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')
        
        # Initialize the ManagerFactory
        self.factory = ManagerFactory(self.app)

        # Use the factory to create managers
        self.db_manager = self.factory.get_manager("DatabaseManager")
        self.quiz_manager = self.factory.get_manager("QuizManager")
        self.user_manager = self.factory.get_manager("UserManager")
        self.analytics_manager = self.factory.get_manager("DataAnalyticsManager")
        self.quiz_retrieval_manager = self.factory.get_manager("QuizRetrievalManager")

        # Set up routes
        self.initialize_routes()

    """
    Description:
    This method registers all routes for the application and maps them to their respective handler functions. 
    It defines the HTTP methods that each route supports, ensuring compatibility with Flask's routing system.

    Semi-formal Notation:
    /*@ requires self.app != null &&
    @ \forall route in route_definitions (route.handler != null &&
    @ route.methods subseteq {"GET", "POST"});
    @ ensures \forall rule in route_definitions (self.app.routes.contains(rule));
    @*/
    """
    def initialize_routes(self):
        # Define routes with various HTTP methods
        route_definitions = [
            ('/', 'index', self.index, ['GET']),
            ('/add_user', 'add_user', self.user_manager.add_user, ['POST']),
            ('/login', 'login', self.user_manager.login, ['GET', 'POST']),
            ('/home', 'home', self.home, ['GET']),
            ('/logout', 'logout', self.user_manager.logout, ['GET']),
            ('/create-quiz', 'create_quiz_route', self.quiz_manager.create_quiz, ['GET', 'POST']),
            ('/submit-quiz', 'submit_quiz_route', self.quiz_manager.submit_quiz, ['POST']),
            ('/quiz-detail/<int:quiz_id>', 'quiz_detail_route', self.quiz_manager.quiz_detail, ['GET']),
            ('/take-quiz/<int:quiz_id>/<int:question_num>', 'take_quiz_route', self.quiz_manager.take_quiz, ['GET', 'POST']),
            ('/score/<int:quiz_id>/<int:score>/<int:total>', 'score_route', self.quiz_manager.score, ['GET']),
            ('/submit-answer/<int:quiz_id>/<int:question_num>', 'submit_quiz_answer_route', self.quiz_manager.submit_quiz_answer, ['POST']),
            ('/penalty/<int:quiz_id>/<int:question_num>', 'penalty_route', self.quiz_manager.penalty, ['GET']),
            ('/delete-quiz/<int:quiz_id>', 'delete_quiz_route', self.quiz_manager.delete_quiz, ['POST']),
            ('/view_other_user_quizzes', 'view_other_user_quizzes', self.quiz_retrieval_manager.view_other_user_quizzes, ['GET', 'POST']),
            ('/restore_user_quizzes', 'restore_user_quizzes', self.quiz_retrieval_manager.restore_user_quizzes, ['POST'])
        ]

        # Loop through route definitions to add them to the app
        for rule, endpoint, view_func, methods in route_definitions:
            self.app.add_url_rule(rule, endpoint, view_func, methods=methods)

    """
    Description:
    This route renders the index page for unauthenticated users or redirects signed-in users to the home page. 
    It uses session tracking to determine the sign-in state of the user.

    Semi-formal Notation:
    /*@ requires self.user_manager.is_signed_in() == (session['email'] != null) &&
    @ session is properly initialized;
    @ ensures \result == (session['email'] != null ? redirect(url_for('home')) : render_template('index.html'));
    @*/
    """
    def index(self):
        if self.user_manager.is_signed_in():
            return redirect(url_for('home'))
        return render_template('index.html')

    """
    Description:
    This route handles rendering the home page for the signed-in user. It retrieves user-specific quizzes and 
    analytics data from the database. If the session contains another user's email, their quizzes are displayed instead.

    Semi-formal Notation:
    /*@ requires session['email'] != null &&
    @ \forall quiz in quizzes (quiz.owner == (session.get('other_user_email') ?: session['email'])) &&
    @ analytics = null if session['other_user_email'] != null;
    @ ensures \result == render_template('home.html', quizzes=quizzes, analytics=analytics);
    @*/
    """
    def home(self):
        if not self.user_manager.is_signed_in():
            return redirect(url_for('login'))
        # Check if there's an other_user_email in session; if so, show their quizzes
        other_user_email = session.get('other_user_email')
        if other_user_email:
            quizzes = self.quiz_manager.get_user_quizzes(other_user_email)
            analytics = None  # Do not show analytics for other user's quizzes
        else:
            session.pop('other_user_email', None)
            user_email = session['email']
            quizzes = self.quiz_manager.get_user_quizzes(user_email)
            analytics = self.analytics_manager.get_user_analytics()    
        return render_template('home.html', quizzes=quizzes, analytics=analytics)

    """
    Description:
    This method starts the Flask app server in debug mode, binding it to the specified port. The port is fetched 
    from the environment variable "PORT" or defaults to 10000 if not set.

    Semi-formal Notation:
    /*@ requires self.app != null &&
    @ os.environ.get("PORT") == null ? port == 10000 : port == int(os.environ.get("PORT"));
    @ ensures self.app.run(host="0.0.0.0", port=port, debug=True);
    @*/
    """
    def run(self):
        port = int(os.environ.get('PORT', 10000))  # Use PORT environment variable
        self.app.run(host='0.0.0.0', port=port, debug=True)
        self.app.run(debug=True)

"""
Description:
This is the main entry point of the application. It initializes the App class and starts the Flask server 
with debugging enabled, ensuring the app is ready to process HTTP requests.

Semi-formal Notation:
/*@ requires App is defined &&
  @ app_instance != null;
  @ ensures app_instance.run(debug=True) starts the Flask app server;
@*/
"""
def main():
    app_instance = App()
    app_instance.run()

if __name__ == '__main__':
    main()