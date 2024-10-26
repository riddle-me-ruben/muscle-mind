from flask import Flask, render_template, request, redirect, url_for, session
from DatabaseManager import DatabaseManager
from QuizManager import QuizManager
from dotenv import load_dotenv
import os

# Load environment variables
load_dotenv()

def create_app():
    # Initialize Flask app
    app = Flask(__name__, static_folder=os.path.join(os.path.dirname(__file__), '../../static'), template_folder='../client')
    app.config['SECRET_KEY'] = os.getenv('SECRET_KEY')

    # Initialize the DatabaseManager instance and configure the database
    db_manager = DatabaseManager(app)

    # Create an instance of the QuizManager class
    quiz_manager = QuizManager(db_manager, session)

    # Helper function to check if the user is signed in
    def is_signed_in():
        return 'email' in session

    # Helper function to check if a user exists in the database
    def user_exists(email):
        existing_user = db_manager.execute_query("SELECT * FROM users WHERE email = %s", (email,))
        return existing_user

    # Define routes within the create_app function to keep state within app context
    @app.route('/')
    def index():
        if is_signed_in():
            return redirect(url_for('home'))  # Redirect if already logged in
        
        return render_template('index.html')  # Show login/signup options

    @app.route('/add_user', methods=['POST'])
    def add_user():
        email = request.form['email']
        password = request.form['password']

        # Check if the email already exists
        if user_exists(email):
            return render_template('index.html', error2="Email already exists.")

        # Insert the new user if the email does not exist
        insert_query = "INSERT INTO users (email, password) VALUES (%s, %s)"
        db_manager.execute_commit(insert_query, (email, password))

        return render_template('index.html', success2="Registration successful! You may now log in.")

    @app.route('/login', methods=['GET', 'POST'])
    def login():
        if request.method == 'POST':
            email = request.form['email']
            password = request.form['password']

            # Verify user credentials
            query = "SELECT * FROM users WHERE email = %s AND password = %s"
            user = db_manager.execute_query(query, (email, password))

            if user:
                session['email'] = email  # Store the user's email in the session
                return redirect(url_for('home'))
            else:
                return render_template('login.html', error='Invalid email or password')

        return render_template('login.html', error=None)

    @app.route('/home')
    def home():
        if not is_signed_in():
            return redirect(url_for('login'))  # Redirect if not logged in
        

        user_email = session['email']  # Get the logged-in user's email
        quizzes = quiz_manager.get_user_quizzes(user_email)  # Fetch quizzes

        return render_template('home.html', quizzes=quizzes)  # Pass quizzes to the template

    @app.route('/logout')
    def logout():
        session.pop('email', None)  # Remove user from session
        return redirect(url_for('index'))

    # Route to render the quiz creation form
    @app.route('/create-quiz', methods=['GET', 'POST'])
    def create_quiz_route():
        if request.method == 'POST':
            return quiz_manager.create_quiz()
        return render_template('create-quiz.html')  # Renders the form for number of questions


    # Route to handle the quiz submission
    @app.route('/submit-quiz', methods=['POST'])
    def submit_quiz_route():
        return quiz_manager.submit_quiz()


    @app.route('/quiz/<int:quiz_id>')
    def quiz_detail_route(quiz_id):
        # Call the QuizManager to get the quiz details
        quiz = quiz_manager.get_quiz_by_id(quiz_id)

        # If the quiz is not found, return an error or flash a message
        if not quiz:
            return "Quiz not found", 404

        # Render the quiz detail page with the quiz data
        return render_template('quiz-detail.html', quiz=quiz)

    @app.route('/take-quiz/<int:quiz_id>/<int:question_num>', methods=['GET', 'POST'])
    def take_quiz_route(quiz_id, question_num):
        # Fetch the quiz details
        quiz = quiz_manager.get_quiz_by_id(quiz_id)

        # Check if the question number is valid
        if question_num >= len(quiz['questions']):
            return redirect(url_for('home'))  # Redirect to home if the quiz is complete
        
        # Render the current question
        return render_template('take-quiz.html', quiz=quiz, question_num=question_num, quiz_id=quiz_id)

    @app.route('/score/<int:quiz_id>/<int:score>/<int:total>')
    def score_route(quiz_id, score, total):
        # Pass the score and total values to the score.html template
        session.pop('current_score', None)
        return render_template('score.html', score=score, total=total)


    
    @app.route('/submit-quiz-answer/<int:quiz_id>/<int:question_num>', methods=['POST'])
    def submit_quiz_answer_route(quiz_id, question_num):
        # Fetch the quiz details
        quiz = quiz_manager.get_quiz_by_id(quiz_id)

        # Get the user's answer for the current question
        user_answer = request.form.get('answer')  # The selected answer from the form

        # Check if the answer is correct
        correct_answer = quiz['questions'][question_num]['correct_option']
        current_score = session.get('current_score', 0)  # Track score using session

        if user_answer == correct_answer:
            # Update score in session
            session['current_score'] = current_score + 1

            # If correct, go to the next question or finish the quiz
            if question_num + 1 < len(quiz['questions']):
                return redirect(url_for('take_quiz_route', quiz_id=quiz_id, question_num=question_num + 1))
            else:
                # If no more questions, show the final score
                total_questions = len(quiz['questions'])
                return redirect(url_for('score_route', quiz_id=quiz_id, score=session['current_score'], total=total_questions))
        else:
            # If incorrect, redirect to the penalty page
            return redirect(url_for('penalty_route', quiz_id=quiz_id, question_num=question_num))



    @app.route('/penalty/<int:quiz_id>/<int:question_num>')
    def penalty_route(quiz_id, question_num):
        # Get the total number of questions for the quiz
        quiz = quiz_manager.get_quiz_by_id(quiz_id)
        total_questions = len(quiz['questions'])

        # Make sure `current_score` exists in the session and has a default value
        current_score = session.get('current_score', 0)

        # Render the penalty page, passing quiz_id, question_num, total_questions, and current_score
        return render_template('penalty.html', quiz_id=quiz_id, question_num=question_num, total_questions=total_questions, score=current_score)
    return app

def main():
    app = create_app()  # Call the function to initialize the app
    app.run(debug=True)  # Start the Flask application

if __name__ == '__main__':
    main()
