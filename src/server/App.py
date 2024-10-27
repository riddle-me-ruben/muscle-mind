from flask import Flask, render_template, redirect, url_for, session
from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from UserManager import UserManager
from dotenv import load_dotenv
import os

class App:
    def __init__(self):
        load_dotenv()
        self.app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
        self.app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')
        
        # Initialize managers
        self.db_manager = DatabaseManager(self.app)
        self.quiz_manager = QuizManager(self.db_manager, session)
        self.user_manager = UserManager(self.db_manager, session)
        
        # Set up routes
        self.init_routes()

    def init_routes(self):
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

    def index(self):
        if self.user_manager.is_signed_in():
            return redirect(url_for('home'))
        return render_template('index.html')

    def home(self):
        if not self.user_manager.is_signed_in():
            return redirect(url_for('login'))
        
        user_email = session['email']
        quizzes = self.quiz_manager.get_user_quizzes(user_email)
        return render_template('home.html', quizzes=quizzes)

    def run(self):
        self.app.run(debug=True)

def main():
    app_instance = App()
    app_instance.run()

if __name__ == '__main__':
    main()