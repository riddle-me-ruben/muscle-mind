from flask import Flask, render_template, redirect, url_for, session
from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from UserManager import UserManager
from dotenv import load_dotenv
import os

"""
The App class initializes and manages the Flask application for the Muscle-Mind system, acting as the central 
mediator between the database subsystem and the quiz management subsystem. This class configures the app, 
sets up environment variables, manages user sessions, and provides a streamlined interface to handle quiz 
creation, user management, and data retrieval from the database.
"""
class App:
    """
    Initialize the App class and set up the Flask app, database manager, and other managers
    @requires Environment variables to be loaded, Flask app to be initialized
    @ensures Flask app and all managers (db_manager, quiz_manager, user_manager) are set up
    """
    def __init__(self):
        load_dotenv()
        self.app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
        self.app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')
        
        # Initialize managers
        self.db_manager = DatabaseManager(self.app)
        self.quiz_manager = QuizManager(self.db_manager)
        self.user_manager = UserManager(self.db_manager, session)
        
        # Set up routes
        self.initialize_routes()

    """
    Initialize the routes for the Flask app
    @requires self.app to be initialized and Flask instance to be active
    @ensures All app routes are defined and linked to corresponding methods
    """
    def initialize_routes(self):
        self.app.add_url_rule('/', 'index', self.index)
        self.app.add_url_rule('/add_user', 'add_user', self.user_manager.add_user, methods=['POST'])
        self.app.add_url_rule('/login', 'login', self.user_manager.login, methods=['GET', 'POST'])
        self.app.add_url_rule('/home', 'home', self.home)
        self.app.add_url_rule('/logout', 'logout', self.user_manager.logout)
        self.app.add_url_rule('/create-quiz', 'create_quiz_route', self.quiz_manager.create_quiz, methods=['GET', 'POST'])
        self.app.add_url_rule('/submit-quiz', 'submit_quiz_route', self.quiz_manager.submit_quiz, methods=['POST'])
        self.app.add_url_rule('/quiz/<int:quiz_id>', 'quiz_detail_route', self.quiz_manager.quiz_detail)
        self.app.add_url_rule('/take-quiz/<int:quiz_id>/<int:question_num>', 'take_quiz_route', self.quiz_manager.take_quiz, methods=['GET', 'POST'])
        self.app.add_url_rule('/score/<int:quiz_id>/<int:score>/<int:total>', 'score_route', self.quiz_manager.score)
        self.app.add_url_rule('/submit-quiz-answer/<int:quiz_id>/<int:question_num>', 'submit_quiz_answer_route', self.quiz_manager.submit_quiz_answer, methods=['POST'])
        self.app.add_url_rule('/penalty/<int:quiz_id>/<int:question_num>', 'penalty_route', self.quiz_manager.penalty)
        self.app.add_url_rule('/delete-quiz/<int:quiz_id>', 'delete_quiz_route', self.quiz_manager.delete_quiz, methods=['POST'])

    """
    Render the index page or redirect to home if user is signed in
    @requires session to track if user is signed in
    @ensures Index page is rendered or redirects to home
    """
    def index(self):
        if self.user_manager.is_signed_in():
            return redirect(url_for('home'))
        return render_template('index.html')

    """
    Render the home page showing quizzes created by the user
    user_email: str - Email of the user from the session
    @requires user must be signed in and user_email stored in session
    @ensures Home page is rendered with the user's quizzes
    """
    def home(self):
        if not self.user_manager.is_signed_in():
            return redirect(url_for('login'))
        
        user_email = session['email']
        quizzes = self.quiz_manager.get_user_quizzes(user_email)
        return render_template('home.html', quizzes=quizzes)

    """
    Start the Flask app in debug mode
    @requires Flask app instance to be initialized
    @ensures The Flask app is running in debug mode
    """
    def run(self):
        self.app.run(debug=True)

"""
Main entry point for running the Flask app
@requires App class to be initialized
@ensures The Flask app runs with debugging enabled
"""
def main():
    app_instance = App()
    app_instance.run()

if __name__ == '__main__':
    main()